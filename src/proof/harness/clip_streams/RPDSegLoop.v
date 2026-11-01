(* Law rt_partial, main: statement 18, the do-while of deflate() calls (rest, flush, avail_in = clip(rest),
   avail_out = clip(out_size - produced), code = deflate(&compressor, flush), while code == Z_OK) (rpd_LI -> rpd_LB,
   DFacts.cd_call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.proof.harness.clip_streams.RPDKit.
Require Import Zlib.proof.harness.clip_streams.RPDMem.
Require Import Zlib.proof.harness.clip_streams.RPDLoopMem.
Require Import Zlib.harness.rt_partial.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rpd_rlt.

(* next - start for next = start + k inside one object *)
Lemma rpd_sub_ptrL (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p) = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. destruct p; try contradiction. simpl.
  unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  f_equal. rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  rewrite Vptrofs_unfold_true by reflexivity. unfold Ptrofs.to_int64.
  rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma rpd_sub_pp (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val k p) p) = Vlong (Int64.repr k).
Proof. intros. apply (rpd_sub_ptrL p k); auto. Qed.

Lemma rpd_sub_arg (p : val) m k : isptr p -> 0 <= k <= m -> m <= Int64.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite rpd_sub_pp by (auto; rep_lia). simpl.
  f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma rpd_binop_sub (p : val) k : isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. unfold eval_binop. rewrite <- (rpd_sub_ptrL p k Pp Hk). unfold force_val2, force_val.
  destruct (sem_binary_operation' _ _ _ _ _); reflexivity.
Qed.

(* data_len - (next - start) *)
Lemma rpd_rest_val (p : val) m k : isptr p -> 0 <= k <= m -> m <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr m))
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p))) =
  Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite rpd_binop_sub by (auto; rep_lia). simpl.
  f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma rpd_sameblock (p : val) k : isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. unfold sameblock; simpl. destruct (peq b b); [reflexivity | congruence]. Qed.


(* the gzip header of a state without one: nothing *)
Lemma rpd_hdr_add' (P : mpred) s hx : d_gzhead s = None -> P |-- P * hdr_at (Some s) nullval hx.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.
Lemma rpd_hdr_drop' s hx : d_gzhead s = None -> hdr_at (Some s) nullval hx |-- emp.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.

(* after the call of an iteration (before `while (code == Z_OK)`): the state after the call, J when the call
   returned Z_OK, the deflate stream of the data when it returned Z_STREAM_END *)
Definition rpd_LC (gv : globals) (vc vd : val) (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (n : Z) (D : list Z) (dp ep op : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX code : Z, EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (0 <= n <= max_size; Zlength D = n; is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits; rs32 code;
        0 <= Zlength O <= b; b <= max_u64; rbytes O; msg_ok msg msgv;
        code = Z_OK -> J wbits D b pos O s tin tout adler;
        code = Z_STREAM_END -> dfinal_of wbits D O; isptr ep)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _out_size (Vlong (Int64.repr b));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rpd_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rpd_comp b O cp; rp_exp n D ep).

(* the body of the do-while *)
Definition rpd_lbody : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [rpd_seg18] in
          (match rpd_seg18 with Ssequence (Sloop c _) _ => c | _ => Sskip end) in exact x).

(* the call of the iteration: deflate(&compressor, flush); code = ... *)
Definition rpd_lcall : statement := ltac:(let x := eval cbv beta iota zeta delta [rp_drop rpd_lbody] in
                                           (rp_drop 5 rpd_lbody) in exact x).

(* the state before the call: avail_in = |dpiece D pos|, avail_out = clip(b - |O|), flush = dflush (n - pos) *)
Definition rpd_X1 (gv : globals) (vc vd : val) (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (D : list Z) (dp ep op : val) (wbits b : Z) (cp : val) (pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (is_bytes D; isptr dp; isptr op; isptr cp; rs32 wbits; J wbits D b pos O s tin tout adler; msg_ok msg msgv;
        isptr ep)
  LOCAL (temp _flush (Vint (Int.repr (dflush (Zlength D - pos))));
         temp _data_len (Vlong (Int64.repr (Zlength D))); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _out_size (Vlong (Int64.repr b));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) (Zlength (dpiece D pos)) tin (offset_val (Zlength O) cp)
         (clipz (b - Zlength O)) tout msgv adler; rpd_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_rp gv;
       malloc_token Ews (tarray tuchar (Zlength D)) dp; data_at Ews (tarray tuchar (Zlength D)) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar (Zlength D)) op; data_at_ Ews (tarray tuchar (Zlength D)) op; rpd_comp b O cp;
       rp_exp (Zlength D) D ep).

Lemma rpd_loop_call {Espec : OracleKind} J0 J gv vc vd D dp ep op wbits b cp pos O s tin tout adler msg msgv :
  clip_dfacts J0 J ->
  semax Delta_rp (rpd_X1 gv vc vd J D dp ep op wbits b cp pos O s tin tout adler msg msgv) rpd_lcall
    (normal_ret_assert (rpd_LC gv vc vd J (Zlength D) D dp ep op wbits b cp)).
Proof.
  intros DF.
  unfold rpd_lcall, rpd_X1. abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  pose proof (cd_range _ _ DF _ _ _ _ _ _ _ _ _ HJ) as RG.
  destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
    (* the call deflate(&compressor, flush) *)
    destruct (cd_call _ _ DF wbits D b pos O s tin tout adler msg HJ)
      as (s' & z' & code & Hrun & Hrc & Hgz' & Hcode & HOK & HEND).
    set (inb := dpiece D pos) in *.
    assert (Hinb : Zlength inb = Z.min (Zlength D - pos) Int.max_unsigned)
      by (unfold inb, dpiece, clipz, umax; rewrite Zlength_sublist; rep_lia).
    assert (Haout : rpd_aout b O = clipz (b - Zlength O)) by (unfold rpd_aout, clipz, umax; reflexivity).
    assert (Ha : 0 <= clipz (b - Zlength O) <= b - Zlength O) by (unfold clipz, umax; rep_lia).
    assert (Hib : 0 <= Zlength inb /\ pos + Zlength inb <= Zlength D) by (rewrite Hinb; rep_lia).
    sep_apply (rpd_in_open (Zlength D) D dp pos (Zlength inb) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
    Intros Rin.
    replace (sublist pos (pos + Zlength inb) D) with inb in *
      by (unfold inb at 1; unfold dpiece; rewrite Hinb; reflexivity).
    sep_apply (rpd_out_open b O cp ltac:(lia) ltac:(unfold max_u64 in *; rep_lia)).
    Intros W Rout.
    rewrite Haout in *.
    match goal with Hx : Rin * _ |-- _ |- _ => rename Hx into Hinc end.
    match goal with Hx : clipz _ = 0 -> wv_ok W |- _ => rename Hx into HW end.
    match goal with Hx : forall zo : list Z, _ |- _ => rename Hx into HCL end.
    set (aout := clipz (b - Zlength O)) in *.
    rewrite dstream_sp_eq. Intros sp.
    unfold R_rp, R_of. Intros.
    replace_SEP 10 (deflate_globals gv * hdr_at (Some s) nullval (Ews, nullval, nullval, nullval)).
    { abstract (entailer!; unfold hdr_at; rewrite Hgz; entailer!). }
    Intros.
    assert (Ppd : isptr (offset_val pos dp)) by (destruct dp; try contradiction; simpl; auto).
    assert (AF : api_fields vc (offset_val pos dp) (Zlength inb) tin (offset_val (Zlength O) cp) aout tout msgv adler =
                 api_fields vc (offset_val 0 (offset_val pos dp)) (Zlength inb) tin (offset_val (Zlength O) cp)
                   (Zlength (Zrepeat Vundef aout)) tout msgv adler)
      by (rewrite isptr_offset_val_zero by auto; rewrite Zlength_Zrepeat by lia; reflexivity).
    rewrite AF. clear AF.
    assert (DA : forall q, @data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar aout) (Zrepeat Vundef aout) q =
                           @data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout)))
                             (Zrepeat Vundef aout) q)
      by (intros; rewrite Zlength_Zrepeat by lia; reflexivity).
    rewrite DA. clear DA.
    forward_call (Some s, vc, nullval, sp, (Ews, nullval, nullval, nullval), offset_val pos dp, Ews, inb, 0,
                  Zlength inb, tin, offset_val (Zlength O) cp, Zrepeat Vundef aout, W, tout, msgv, msg, adler,
                  dflush (Zlength D - pos), (Some s', z', code), gv).
    { abstract (
        rewrite Zlength_Zrepeat by lia;
        split; [exact HW | ];
        split; [unfold dflush, s32_ok; destruct (_ <=? _); compute; split; intro X; discriminate | ];
        split;
        [ unfold strm_ranges, zmk; simpl; rewrite Zlength_nil;
          assert (Hib' : Zlength inb <= Int.max_unsigned) by (rewrite Hinb; rep_lia);
          assert (Ha' : aout <= Int.max_unsigned) by (unfold aout, clipz, umax; rep_lia);
          unfold u32_ok, u64_ok, max_u64 in *; repeat split; try rep_lia;
          [ unfold inb, dpiece; apply Forall_sublist; exact RD | constructor ]
        | exists (fun f => f); split; [ apply ef_ok_id | ];
          unfold on_state, c_on_state; rewrite c_deflate_g_id;
          change (zmk inb 0 (Zlength inb) tin aout tout adler msg)
            with (rzcall inb 0 (Zlength inb) tin aout tout adler msg);
          rewrite Hrun; reflexivity ]). }
    simpl fst; simpl snd.
    Intros msgv'.
    forward.
    destruct Hrc as (Hzi & Hai & Hni & Hti & Hao & Hzo & Hto & Rzo).
    sep_apply Hinc.
    rewrite Zlength_Zrepeat by lia.
    sep_apply (HCL (z_out z') ltac:(rep_lia)).
    sep_apply (rpd_hdr_drop' s (Ews, nullval, nullval, nullval) Hgz).
    sep_apply (BoundKit.dstream_sp_dstream 2 (Some s') vc nullval sp gv).
    rewrite !offset_offset_val, Hni.
    replace (Zlength O + Zlength (z_out z')) with (Zlength (O ++ z_out z')) by (rewrite Zlength_app; lia).
    Exists code (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z')
           (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
    assert (P1 : rs32 code)
      by (unfold rs32; destruct Hcode as [-> | [-> | ->]]; compute; split; intro X; discriminate).
    assert (P2 : 0 <= Zlength (O ++ z_out z') <= b) by (rewrite Zlength_app; unfold clipz, umax in *; rep_lia).
    assert (P3 : rbytes (O ++ z_out z')) by (unfold rbytes in *; rewrite Forall_app; auto).
    assert (P4 : code = Z_STREAM_END -> dfinal_of wbits D (O ++ z_out z'))
      by (intros E; destruct (HEND E) as (_ & _ & HF); exact HF).
    unfold R_rp, R_of.
    abstract entailer!.
Qed.

(* one iteration: from the loop head to the state after deflate() *)
Lemma rpd_loop_body {Espec : OracleKind} J0 J gv vc vd n D dp ep op wbits b cp :
  clip_dfacts J0 J ->
  semax Delta_rp (rpd_LI gv vc vd J n D dp ep op wbits b cp) rpd_lbody
    (normal_ret_assert (rpd_LC gv vc vd J n D dp ep op wbits b cp)).
Proof.
  intros DF.
  unfold rpd_lbody. abbreviate_semax.
  unfold rpd_LI. Intros pos O s tin tout adler ai ao msg msgv.
    pose proof (cd_range _ _ DF _ _ _ _ _ _ _ _ _ ltac:(eassumption)) as RG.
    destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
    rewrite rpd_api_fields_L. unfold api_fieldsL. Intros.
    subst n.
    forward.
    forward.
    { entailer!. apply prop_right. apply rpd_sameblock; auto. }
    rewrite rpd_rest_val by (auto; unfold max_size in *; rep_lia).
    forward.
    forward_if (temp _flush (Vint (Int.repr (dflush (Zlength D - pos))))).
    { forward. entailer!. unfold dflush, umax.
      rewrite !Int64.unsigned_repr in * by (unfold max_size in *; rep_lia).
      match goal with |- context [Z.leb ?x _] => destruct (Z.leb_spec x 4294967295) end; [reflexivity | lia]. }
    { forward. entailer!. unfold dflush, umax.
      rewrite !Int64.unsigned_repr in * by (unfold max_size in *; rep_lia).
      match goal with |- context [Z.leb ?x _] => destruct (Z.leb_spec x 4294967295) end; [lia | reflexivity]. }
    forward_call (Zlength D - pos).
    { unfold max_size in *; rep_lia. }
    forward.
    forward.
    forward_call (b - Zlength O).
    { apply prop_right. apply rpd_sameblock; auto. }
    { entailer!. simpl. rewrite rpd_sub_arg by (auto; unfold max_u64 in *; rep_lia). reflexivity. }
    { unfold max_u64 in *; rep_lia. }
    forward.
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (rpd_loop_call J0 J gv vc vd D dp ep op wbits b cp pos O s tin tout adler msg msgv DF) ].
    unfold rpd_X1.
    assert (Hinb : Zlength (dpiece D pos) = Z.min (Zlength D - pos) Int.max_unsigned)
      by (unfold dpiece, clipz, umax; rewrite Zlength_sublist; rep_lia).
    assert (Hcl : clipz (b - Zlength O) = Z.min (b - Zlength O) Int.max_unsigned) by reflexivity.
    rewrite <- Hinb, <- Hcl.
    assert (U1 : u32_ok (Zlength (dpiece D pos))) by (rewrite Hinb; unfold u32_ok; rep_lia).
    assert (U2 : u32_ok (clipz (b - Zlength O))) by (rewrite Hcl; unfold u32_ok, max_u64 in *; rep_lia).
    sep_apply (rpd_api_fields_fold vc (offset_val pos dp) (Zlength (dpiece D pos)) tin (offset_val (Zlength O) cp)
                 (clipz (b - Zlength O)) tout msgv adler U1 H5 U2 H7 H8).
    abstract entailer!.
Qed.

Lemma rpd_seg_loop : rpd_loop_stmt.
Proof.
  intros Espec J0 J gv vc vd n D dp ep op wbits b cp DF K.
  unfold rpd_seg18, POST_B, POST_rp. abbreviate_semax.
  forward_loop (rpd_LI gv vc vd J n D dp ep op wbits b cp) continue: (rpd_LC gv vc vd J n D dp ep op wbits b cp)
    break: (rpd_LB gv vc vd n D dp ep op wbits b cp).
  { apply ENTAIL_refl. }
  { eapply semax_post; [ | | | | apply (rpd_loop_body J0 J gv vc vd n D dp ep op wbits b cp DF) ];
      intros; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return; normalize. }
  { (* while (code == Z_OK) *)
    unfold rpd_LC. Intros code pos O s tin tout adler ai ao msg msgv.
    forward_if.
    { forward. unfold rpd_LI. Exists pos O s tin tout adler ai ao msg msgv.
      assert (code = 0) by (apply repr_inj_signed; auto; unfold rs32 in *; rep_lia).
      entailer!. }
    { forward. unfold rpd_LB. Exists code O (Some s) (offset_val pos dp) ai tin ao tout adler msgv.
      entailer!. } }
  (* after the loop *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  exact K.
Qed.

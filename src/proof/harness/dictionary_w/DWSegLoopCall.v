(* Laws rt_dictionary and api_dict_id, main (DWKit.v): the deflate() call of an iteration of statement 21
   (rt_dictionary's numbers; 20 in api_dict_id), the do-while of deflate() calls (`code = deflate(&compressor,
   flush)`, DWFacts.dw_call), in each program's context (the same proof; the temporaries differ).  As
   clip_streams/RTSegLoop.v's rt_loop_call, with the dictionary's object kept in the frame. *)
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
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Import Zlib.proof.harness.clip_streams.RTLoopMem.
Require Import Zlib.proof.harness.clip_streams.RTSegLoop.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.harness.rt_dictionary.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the body of the do-while, and its call (the last two statements of the body), in each program *)
Definition dw_lbody_drt : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [seg_loop_drt] in
          (match seg_loop_drt with Sloop c _ => c | _ => Sskip end) in exact x).
Definition dw_lbody_dai : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [seg_loop_dai] in
          (match seg_loop_dai with Sloop c _ => c | _ => Sskip end) in exact x).
Definition dw_lcall_drt : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [rt_drop dw_lbody_drt] in (rt_drop 5 dw_lbody_drt) in exact x).
Definition dw_lcall_dai : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [rt_drop dw_lbody_dai] in (rt_drop 5 dw_lbody_dai) in exact x).

(* the body without its first three statements (the load of next_in and rest, flush, its test): the two clip()
   calls and the call of deflate() *)
Definition dw_lrest_drt : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [rt_drop dw_lbody_drt] in (rt_drop 3 dw_lbody_drt) in exact x).
Definition dw_lrest_dai : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [rt_drop dw_lbody_dai] in (rt_drop 3 dw_lbody_dai) in exact x).

Section Assertions.
Context (vlit : ident) (gv : globals) (vc vd : val).

(* after the call of an iteration (before `while (code == Z_OK)`): J when the call returned Z_OK, the zlib stream
   of the data with the dictionary when it returned Z_STREAM_END *)
Definition dw_LC (J : Z -> list Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z)
    (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX code : Z, EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z,
  EX ao : Z, EX msg : option Z, EX msgv : val,
  PROP (dw_cf n D dp op dict ddp wbits; isptr cp; rs32 code; 0 <= Zlength O <= b; b <= max_u64; rbytes O;
        msg_ok msg msgv;
        code = 0 -> J wbits dict D b pos O s tin tout adler;
        code = 1 -> dfinal_dict wbits dict D O)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _out_size (Vlong (Int64.repr b)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rt_comp b O cp).

(* the state before the call: avail_in = |dpiece D pos|, avail_out = clip(b - |O|), flush = dflush (n - pos) *)
Definition dw_X1 (J : Z -> list Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits b : Z) (cp : val) (pos : Z) (O : list Z)
    (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (dw_cf (Zlength D) D dp op dict ddp wbits; isptr cp; J wbits dict D b pos O s tin tout adler;
        msg_ok msg msgv)
  LOCAL (temp _flush (Vint (Int.repr (dflush (Zlength D - pos))));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr (Zlength D)));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _out_size (Vlong (Int64.repr b)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) (Zlength (dpiece D pos)) tin (offset_val (Zlength O) cp)
         (clipz (b - Zlength O)) tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar (Zlength D)) dp; data_at Ews (tarray tuchar (Zlength D)) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar (Zlength D)) op; data_at_ Ews (tarray tuchar (Zlength D)) op;
       rt_comp b O cp).

(* the state after the first three statements of the body: rest = n - pos, flush = dflush (n - pos) *)
Definition dw_X0 (J : Z -> list Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits b : Z) (cp : val) (pos : Z) (O : list Z)
    (s : dstate) (tin tout adler ai ao : Z) (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (dw_cf (Zlength D) D dp op dict ddp wbits; isptr cp; J wbits dict D b pos O s tin tout adler;
        msg_ok msg msgv)
  LOCAL (temp _flush (Vint (Int.repr (dflush (Zlength D - pos))));
         temp _rest (Vlong (Int64.repr (Zlength D - pos)));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr (Zlength D)));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _out_size (Vlong (Int64.repr b)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar (Zlength D)) dp; data_at Ews (tarray tuchar (Zlength D)) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar (Zlength D)) op; data_at_ Ews (tarray tuchar (Zlength D)) op;
       rt_comp b O cp).

End Assertions.

(* rt_dictionary *)
Lemma dw_loop_call_drt {Espec : OracleKind} J0 J1 J vlit gv vc vd D dp op dict ddp wbits b cp pos O s tin tout
    adler msg msgv :
  dict_dfacts J0 J1 J ->
  semax Delta_drt (dw_X1 vlit gv vc vd J D dp op dict ddp wbits b cp pos O s tin tout adler msg msgv) dw_lcall_drt
    (normal_ret_assert (dw_LC vlit gv vc vd J (Zlength D) D dp op dict ddp wbits b cp)).
Proof.
  intros DF.
  unfold dw_lcall_drt, dw_X1. abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  pose proof (dw_range _ _ _ DF _ _ _ _ _ _ _ _ _ _ HJ) as RG.
  destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  destruct (dw_call _ _ _ DF wbits dict D b pos O s tin tout adler msg HJ)
    as (s' & z' & code & Hrun & Hrc & Hgz' & Hcode & HOK & HEND).
  set (inb := dpiece D pos) in *.
  assert (Hinb : Zlength inb = Z.min (Zlength D - pos) Int.max_unsigned)
    by (unfold inb, dpiece, clipz, umax; rewrite Zlength_sublist; rep_lia).
  assert (Haout : rt_aout b O = clipz (b - Zlength O)) by (unfold rt_aout, clipz, umax; reflexivity).
  assert (Ha : 0 <= clipz (b - Zlength O) <= b - Zlength O) by (unfold clipz, umax; rep_lia).
  assert (Hib : 0 <= Zlength inb /\ pos + Zlength inb <= Zlength D) by (rewrite Hinb; rep_lia).
  sep_apply (rt_in_open (Zlength D) D dp pos (Zlength inb) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
  Intros Rin.
  replace (sublist pos (pos + Zlength inb) D) with inb in *
    by (unfold inb at 1; unfold dpiece; rewrite Hinb; reflexivity).
  sep_apply (rt_out_open b O cp ltac:(lia) ltac:(unfold max_u64 in *; rep_lia)).
  Intros W Rout.
  rewrite Haout in *.
  match goal with Hx : Rin * _ |-- _ |- _ => rename Hx into Hinc end.
  match goal with Hx : clipz _ = 0 -> wv_ok W |- _ => rename Hx into HW end.
  match goal with Hx : forall zo : list Z, _ |- _ => rename Hx into HCL end.
  set (aout := clipz (b - Zlength O)) in *.
  rewrite dstream_sp_eq. Intros sp.
  unfold R_of. Intros.
  replace_SEP 10 (deflate_globals gv * hdr_at (Some s) nullval (Ews, nullval, nullval, nullval)).
  { entailer!; unfold hdr_at; rewrite Hgz; entailer!. }
  Intros.
  assert (Ppd : isptr (offset_val pos dp)) by (destruct H as (_ & _ & _ & Pdp & _); destruct dp; try contradiction; simpl; auto).
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
  { rewrite Zlength_Zrepeat by lia;
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
        rewrite Hrun; reflexivity ]. }
  simpl fst; simpl snd.
  Intros msgv'.
  forward.
  destruct Hrc as (Hzi & Hai & Hni & Hti & Hao & Hzo & Hto & Rzo).
  sep_apply Hinc.
  rewrite Zlength_Zrepeat by lia.
  sep_apply (HCL (z_out z') ltac:(rep_lia)).
  sep_apply (rt_hdr_drop' s (Ews, nullval, nullval, nullval) Hgz).
  sep_apply (BoundKit.dstream_sp_dstream 2 (Some s') vc nullval sp gv).
  rewrite !offset_offset_val, Hni.
  replace (Zlength O + Zlength (z_out z')) with (Zlength (O ++ z_out z')) by (rewrite Zlength_app; lia).
  Exists code (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z')
         (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
  assert (P1 : rs32 code)
    by (unfold rs32; destruct Hcode as [ -> | [ -> | -> ] ]; compute; split; intro X; discriminate).
  assert (P2 : 0 <= Zlength (O ++ z_out z') <= b) by (rewrite Zlength_app; unfold clipz, umax in *; rep_lia).
  assert (P3 : rbytes (O ++ z_out z')) by (unfold rbytes in *; rewrite Forall_app; auto).
  assert (P4 : code = 1 -> dfinal_dict wbits dict D (O ++ z_out z'))
    by (intros E; destruct (HEND E) as (_ & _ & HF); exact HF).
  assert (P5 : code = 0 -> J wbits dict D b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
                             (z_total_in z') (z_total_out z') (z_adler z'))
    by (intros E; apply HOK; exact E).
  unfold R_of.
  entailer!.
Qed.

(* api_dict_id: the same proof in its context *)
Lemma dw_loop_call_dai {Espec : OracleKind} J0 J1 J vlit gv vc vd D dp op dict ddp wbits b cp pos O s tin tout
    adler msg msgv :
  dict_dfacts J0 J1 J ->
  semax Delta_dai (dw_X1 vlit gv vc vd J D dp op dict ddp wbits b cp pos O s tin tout adler msg msgv) dw_lcall_dai
    (normal_ret_assert (dw_LC vlit gv vc vd J (Zlength D) D dp op dict ddp wbits b cp)).
Proof.
  intros DF.
  unfold dw_lcall_dai, dw_X1. abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  pose proof (dw_range _ _ _ DF _ _ _ _ _ _ _ _ _ _ HJ) as RG.
  destruct RG as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  destruct (dw_call _ _ _ DF wbits dict D b pos O s tin tout adler msg HJ)
    as (s' & z' & code & Hrun & Hrc & Hgz' & Hcode & HOK & HEND).
  set (inb := dpiece D pos) in *.
  assert (Hinb : Zlength inb = Z.min (Zlength D - pos) Int.max_unsigned)
    by (unfold inb, dpiece, clipz, umax; rewrite Zlength_sublist; rep_lia).
  assert (Haout : rt_aout b O = clipz (b - Zlength O)) by (unfold rt_aout, clipz, umax; reflexivity).
  assert (Ha : 0 <= clipz (b - Zlength O) <= b - Zlength O) by (unfold clipz, umax; rep_lia).
  assert (Hib : 0 <= Zlength inb /\ pos + Zlength inb <= Zlength D) by (rewrite Hinb; rep_lia).
  sep_apply (rt_in_open (Zlength D) D dp pos (Zlength inb) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
  Intros Rin.
  replace (sublist pos (pos + Zlength inb) D) with inb in *
    by (unfold inb at 1; unfold dpiece; rewrite Hinb; reflexivity).
  sep_apply (rt_out_open b O cp ltac:(lia) ltac:(unfold max_u64 in *; rep_lia)).
  Intros W Rout.
  rewrite Haout in *.
  match goal with Hx : Rin * _ |-- _ |- _ => rename Hx into Hinc end.
  match goal with Hx : clipz _ = 0 -> wv_ok W |- _ => rename Hx into HW end.
  match goal with Hx : forall zo : list Z, _ |- _ => rename Hx into HCL end.
  set (aout := clipz (b - Zlength O)) in *.
  rewrite dstream_sp_eq. Intros sp.
  unfold R_of. Intros.
  replace_SEP 10 (deflate_globals gv * hdr_at (Some s) nullval (Ews, nullval, nullval, nullval)).
  { entailer!; unfold hdr_at; rewrite Hgz; entailer!. }
  Intros.
  assert (Ppd : isptr (offset_val pos dp)) by (destruct H as (_ & _ & _ & Pdp & _); destruct dp; try contradiction; simpl; auto).
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
  { rewrite Zlength_Zrepeat by lia;
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
        rewrite Hrun; reflexivity ]. }
  simpl fst; simpl snd.
  Intros msgv'.
  forward.
  destruct Hrc as (Hzi & Hai & Hni & Hti & Hao & Hzo & Hto & Rzo).
  sep_apply Hinc.
  rewrite Zlength_Zrepeat by lia.
  sep_apply (HCL (z_out z') ltac:(rep_lia)).
  sep_apply (rt_hdr_drop' s (Ews, nullval, nullval, nullval) Hgz).
  sep_apply (BoundKit.dstream_sp_dstream 2 (Some s') vc nullval sp gv).
  rewrite !offset_offset_val, Hni.
  replace (Zlength O + Zlength (z_out z')) with (Zlength (O ++ z_out z')) by (rewrite Zlength_app; lia).
  Exists code (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z')
         (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
  assert (P1 : rs32 code)
    by (unfold rs32; destruct Hcode as [ -> | [ -> | -> ] ]; compute; split; intro X; discriminate).
  assert (P2 : 0 <= Zlength (O ++ z_out z') <= b) by (rewrite Zlength_app; unfold clipz, umax in *; rep_lia).
  assert (P3 : rbytes (O ++ z_out z')) by (unfold rbytes in *; rewrite Forall_app; auto).
  assert (P4 : code = 1 -> dfinal_dict wbits dict D (O ++ z_out z'))
    by (intros E; destruct (HEND E) as (_ & _ & HF); exact HF).
  assert (P5 : code = 0 -> J wbits dict D b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
                             (z_total_in z') (z_total_out z') (z_adler z'))
    by (intros E; apply HOK; exact E).
  unfold R_of.
  entailer!.
Qed.

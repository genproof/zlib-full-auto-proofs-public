(* Law rfc_level0_size, main: the deflate() call of one iteration of the do-while (statement 20):
   `code = deflate(&strm, flush)` with avail_in = |piece| and avail_out = clip(room - produced), from l0_X1 (the
   state before the call, k blocks drawn) to l0_LC (the state at the loop test: J when the call returned Z_OK,
   the whole stream and total_out = size when it returned anything else), by Level0CallsFit.ff_call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0CallsFit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2LoopMem.
Require Import Zlib.harness.rfc_level0_size.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= l0_rlt.

(* what a call that did not return Z_OK leaves: Z_STREAM_END, the stored stream of the data in the output
   object, total_out = size *)
Definition l0_endf (n : Z) (D : list Z) (wbits room : Z) (code : Z) (O : list Z) (tout : Z) : Prop :=
  code = Z_STREAM_END /\ tout = l0_size wbits n /\ 0 <= Zlength O <= room /\ bytes O /\ l0_final wbits D O.

(* after the call of an iteration (at the loop test `while (code == Z_OK)`) *)
Definition l0_LC (gv : globals) (vs : val) (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (n : Z) (D : list Z) (dp cp : val) (wbits room : Z) : environ -> mpred :=
  EX code : Z, EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (Zlength D = n; isptr dp; isptr cp; msg_ok msg msgv;
        code = Z_OK -> J wbits D room pos O s tin tout adler;
        code <> Z_OK -> l0_endf n D wbits room code O tout)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _data_len (Vlong (Int64.repr n)); temp _size (Vlong (Int64.repr (l0_size wbits n)));
         temp _room (Vlong (Int64.repr room)); temp _data dp; temp _compressed cp; lvar _strm t_zsl vs; gvars gv)
  SEP (dstream 2 (Some s) vs nullval gv;
       api_fields vs (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; l0_srest vs;
       mem_mgr gv; R gv; l0_data n D dp; l0_comp room O cp).

(* the body of the do-while *)
Definition l0_lbody : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [l0_seg20] in
          (match l0_seg20 with Ssequence (Sloop c _) _ => c | _ => Sskip end) in exact x).

(* the call of the iteration: deflate(&strm, flush); code = ... *)
Definition l0_lcall : statement := ltac:(let x := eval cbv beta iota zeta delta [l0_drop l0_lbody] in
                                           (l0_drop 6 l0_lbody) in exact x).

(* the state before the call, k blocks drawn: avail_in = |l0_inb D pos k|, avail_out = clip(room - |O|),
   flush = l0_flush *)
Definition l0_X1 (gv : globals) (vs : val) (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    (D : list Z) (dp cp : val) (wbits room : Z) (k pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (isptr dp; isptr cp; 1 <= k <= 65531; J wbits D room pos O s tin tout adler; msg_ok msg msgv)
  LOCAL (temp _flush (Vint (Int.repr (l0_flush (Zlength D) pos k)));
         temp _data_len (Vlong (Int64.repr (Zlength D)));
         temp _size (Vlong (Int64.repr (l0_size wbits (Zlength D))));
         temp _room (Vlong (Int64.repr room)); temp _data dp; temp _compressed cp; lvar _strm t_zsl vs; gvars gv)
  SEP (dstream 2 (Some s) vs nullval gv;
       api_fields vs (offset_val pos dp) (Zlength (l0_inb D pos k)) tin (offset_val (Zlength O) cp)
         (l0_clip (room - Zlength O)) tout msgv adler; l0_srest vs;
       mem_mgr gv; R gv; l0_data (Zlength D) D dp; l0_comp room O cp).

(* the input object's length *)
Lemma l0_inb_len D pos k :
  0 <= pos <= Zlength D -> 1 <= k ->
  Zlength (l0_inb D pos k) = l0_piece (Zlength D) pos k.
Proof.
  intros. unfold l0_inb, l0_piece.
  destruct (Z.leb_spec (Zlength D - pos) (65535 * k)); rewrite Zlength_sublist; lia.
Qed.

Lemma l0_piece_range n pos k :
  0 <= pos <= n -> 1 <= k <= 65532 -> 0 <= l0_piece n pos k <= Z.min (n - pos) 4294639620.
Proof. intros. unfold l0_piece. destruct (Z.leb_spec (n - pos) (65535 * k)); lia. Qed.

(* the gzip header of a state without one: nothing *)
Lemma l0_hdr_add (P : mpred) s hx : d_gzhead s = None -> P |-- P * hdr_at (Some s) nullval hx.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.
Lemma l0_hdr_drop s hx : d_gzhead s = None -> hdr_at (Some s) nullval hx |-- emp.
Proof. intros H. unfold hdr_at. rewrite H. entailer!. Qed.

Lemma l0_loop_call {Espec : OracleKind} J gv vs D dp cp wbits room k pos O s tin tout adler msg msgv :
  l0_fit_facts l0s_kmax l0s_slack J ->
  semax Delta_l0 (l0_X1 gv vs J D dp cp wbits room k pos O s tin tout adler msg msgv) l0_lcall
    (normal_ret_assert (l0_LC gv vs J (Zlength D) D dp cp wbits room)).
Proof.
  intros LF.
  unfold l0_lcall, l0_X1. abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  destruct (ff_range _ _ J LF _ _ _ _ _ _ _ _ _ HJ)
    as (Hpos & Hn & HO & Hb & RD & RO & Hgz & Htin & Htout & Had).
  destruct (ff_call _ _ J LF wbits D room pos O s tin tout adler msg k HJ ltac:(unfold l0s_kmax; lia))
    as (s' & z' & code & Hrun & Hzi & Hai & Hni & Hti & Hao & Hzo & Hto & Rzo & Hgz' & HOK & HEND).
  set (inb := l0_inb D pos k) in *.
  set (aout := l0_clip (room - Zlength O)) in *.
  pose proof (l0_inb_len D pos k ltac:(lia) ltac:(lia)) as Hinb. fold inb in Hinb.
  pose proof (l0_piece_range (Zlength D) pos k ltac:(lia) ltac:(lia)) as Hpr.
  assert (Ha : 0 < aout <= room - Zlength O) by (unfold aout, l0_clip; lia).
  unfold l0_data. Intros.
  sep_apply (l0_in_open (Zlength D) D dp pos (Zlength inb) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
  Intros Rin.
  replace (sublist pos (pos + Zlength inb) D) with inb in *
    by (unfold inb at 1; unfold l0_inb; rewrite Hinb; reflexivity).
  sep_apply (l0_out_open room O cp aout ltac:(lia) ltac:(lia) ltac:(lia)).
  Intros Rout.
  match goal with Hx : Rin * _ |-- _ |- _ => rename Hx into Hinc end.
  match goal with Hx : forall zo : list Z, _ |- _ => rename Hx into HCL end.
  rewrite dstream_sp_eq. Intros sp.
  unfold R. Intros.
  replace_SEP 8 (deflate_globals gv * hdr_at (Some s) nullval (Ews, nullval, nullval, nullval)).
  { (entailer!; unfold hdr_at; rewrite Hgz; entailer!). }
  Intros.
  assert (Ppd : isptr (offset_val pos dp)) by (destruct dp; try contradiction; simpl; auto).
  assert (AF : api_fields vs (offset_val pos dp) (Zlength inb) tin (offset_val (Zlength O) cp) aout tout msgv adler =
               api_fields vs (offset_val 0 (offset_val pos dp)) (Zlength inb) tin (offset_val (Zlength O) cp)
                 (Zlength (Zrepeat Vundef aout)) tout msgv adler)
    by (rewrite isptr_offset_val_zero by auto; rewrite Zlength_Zrepeat by lia; reflexivity).
  rewrite AF. clear AF.
  assert (DA : forall q, data_at Ews (tarray tuchar aout) (Zrepeat Vundef aout) q =
                         data_at Ews (tarray tuchar (Zlength (Zrepeat Vundef aout))) (Zrepeat Vundef aout) q)
    by (intros; rewrite Zlength_Zrepeat by lia; reflexivity).
  rewrite DA. clear DA.
  replace_SEP 1 (Rout * wv_at WVnone (offset_val (Zlength O) cp)).
  { unfold wv_at. entailer!. }
  Intros.
  forward_call (Some s, vs, nullval, sp, (Ews, nullval, nullval, nullval), offset_val pos dp, Ews, inb, 0,
                Zlength inb, tin, offset_val (Zlength O) cp, Zrepeat Vundef aout, WVnone, tout, msgv, msg, adler,
                l0_flush (Zlength D) pos k, (Some s', z', code), gv).
  { (
      rewrite Zlength_Zrepeat by lia;
      split; [intros; lia | ];
      split; [unfold l0_flush, s32_ok; destruct (_ <=? _); compute; split; intro X; discriminate | ];
      split;
      [ unfold strm_ranges, zmk; simpl; rewrite Zlength_nil;
        assert (Ha' : aout <= Int.max_unsigned) by (unfold aout, l0_clip; rep_lia);
        unfold u32_ok, u64_ok, l0_max_u64 in *; repeat split; try rep_lia;
        [ unfold inb, l0_inb; apply Forall_sublist; exact RD | constructor ]
      | exists (fun f => f); split; [ apply ef_ok_id | ];
        unfold on_state, c_on_state; rewrite c_deflate_g_id;
        change (zmk inb 0 (Zlength inb) tin aout tout adler msg)
          with (zcall inb 0 (Zlength inb) tin aout tout adler msg);
        rewrite Hrun; reflexivity ]). }
  simpl fst; simpl snd.
  Intros msgv'.
  forward.
  sep_apply Hinc.
  rewrite Zlength_Zrepeat by lia.
  sep_apply (HCL (z_out z') ltac:(rep_lia)).
  sep_apply (l0_hdr_drop s (Ews, nullval, nullval, nullval) Hgz).
  sep_apply (BoundKit.dstream_sp_dstream 2 (Some s') vs nullval sp gv).
  rewrite !offset_offset_val, Hni.
  replace (Zlength O + Zlength (z_out z')) with (Zlength (O ++ z_out z')) by (rewrite Zlength_app; lia).
  Exists code (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s' (z_total_in z') (z_total_out z')
         (z_adler z') (z_avail_in z') (z_avail_out z') (z_msg z') msgv'.
  assert (P4 : code <> Z_OK -> l0_endf (Zlength D) D wbits room code (O ++ z_out z') (z_total_out z')).
  { intros E. destruct (HEND E) as (Ec & Hh & Tt & E1 & E2 & E3 & E4).
    split; [exact Ec|]. split; [exact E4|]. split; [rewrite Zlength_app; lia|].
    split; [unfold bytes in *; apply Forall_app; auto|]. exists Hh, Tt; auto. }
  unfold R, l0_data, wv_at.
  entailer!.
Qed.

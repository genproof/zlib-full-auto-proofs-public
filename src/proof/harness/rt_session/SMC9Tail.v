(* Law rt_session (harness/rt_session.c): the end of main's statements 63-72 with a gzip header (statements 69-72:
   the raw-dictionary test, asked = 0, next_in = input, next_out = out), from the state right after
   inflateGetHeader returned Z_OK (SMSegC9.v) to the inflate loop's invariant II_9.

   With a header main has no dictionary (with_dict = 0: window_bits > 15), so inflateSetDictionary is not called.
   The invariant at the loop's head is SIFacts.si_head's for the stream inflateInit2_ made and inflateGetHeader
   attached got to (RTIIface.head_live); its header part is RTH9Spec.head_mem9 (SMC9Kit.c9_head9).  A file of its
   own: the two stores into the 14-field struct are slow to elaborate. *)
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
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMC9Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* statements 69-72 of main's body *)
Definition c9_tail : statement := ltac:(get_stmt (suf 6 (take 10 (suf 63 body0)))).

(* main's temporaries d_locals u (su_wbits u) with a header: with_dict = 0, with_head = 1 *)
Definition c9_dlocals (u : setup) : list localdef :=
  [temp _level (vi (su_level u)); temp _window_bits (vi (su_wbits u)); temp _mem_level (vi (su_mem u));
   temp _strategy (vi (su_strategy u)); temp _choice (vi (su_choice u));
   temp _with_dict (vi (Z.b2z false)); temp _with_head (vi (Z.b2z true));
   temp _dict_len (vl (Zlength (su_dict u))); temp _extra_len (vl (Zlength (su_xf u)));
   temp _name_len (vl (Zlength (su_nm u))); temp _comment_len (vl (Zlength (su_cm u)));
   temp _data_len (vl (Zlength (su_data u))); temp _out_size (vl (su_cap u));
   temp _text (vi (su_text u)); temp _time (vl (su_time u)); temp _os (vi (su_os u)); temp _hcrc (vi (su_hcrc u));
   temp _dict (su_dictp u); temp _data (su_dp u)].

(* the state after inflateGetHeader(&decompressor, &got) returned Z_OK and main asserted it: the stream of
   inflateInit2_ (state sp) with got attached, its fields as new_stream and inflateInit2_ left them *)
Definition c9_pre (gv : globals) (vh vg vc va vd : val) (u : setup) (O : list Z) (c : cst) (src : list Z)
    (ip sp : val) : environ -> mpred :=
  let L := Zlib.proof.roundtrip.RTIIface.head_live (init_live sp (su_wbits u)) (h0 u) vg Tsh
             (su_gxp u) (su_gnp u) (su_gcp u) in
  PROPx []
  (LOCALx (temp _t'66 (Vint (Int.repr Z_OK)) :: temp _code (Vint (Int.repr Z_OK)) ::
           temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: c_locals u ++ c9_dlocals u ++ lvs gv vh vg vc va vd)
  (SEPx [Zlib.proof.roundtrip.RTH8Spec.istream8_opt gv Tsh vd c9_z0 (Some L);
         Zlib.proof.roundtrip.RTH8Spec.head_mem8 L; zfuncs gv; gtoks u;
         @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength c9_hv)) c9_hv (gv ___stringlit_rt_session_1);
         version_lit gv; mem_mgr gv; cstream gv vc (ghp vh u) c; deflate_globals gv; tables_rep Ers gv;
         dobj u; cobj u O; oobj u []; data_at_ Tsh t_p va; iobj src ip; hobj vh u; dictobj u; dcopy u])).

Lemma c9_tail_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip sp :
  ses_ifacts (fun _ => True) P PN -> with_head u = true -> su_ok u -> sc_ok (scase_of u) (su_data u) O ->
  Zlength O <= su_cap u -> rbytes O -> src_ok O src -> isptr ip -> vd <> nullval ->
  Zlib.proof.inflate.Records.i_mode (l_s (init_live sp (su_wbits u))) = Zlib.proof.inflate.Model.HEAD ->
  semax Delta_s (c9_pre gv vh vg vc va vd u O c src ip sp) c9_tail
    (overridePost (EX l : ils, II_9 gv vh vg vc va vd P u O c src ip l) POST_s).
Proof.
  intros PF WH Hu H0 H1 H2 H4 Pip Nd Wmode.
  pose proof Hu as (Hd & _).
  destruct (c9_wb u Hd WH) as [Hwb Hiw].
  unfold c9_pre, c9_tail, II_9, POST_s, c_locals, c9_dlocals, d_locals, lvs, lv_locals. cbn [app].
  rewrite WH, (c9_nodict u WH).
  unfold Delta_s. simplify_func_tycontext. abbreviate_semax.
  (* with_dict is 0 with a header: no inflateSetDictionary *)
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp _t'68 (Vint (Int.repr 0)) :: Q) (SEPx R))) end.
  { exfalso; lia. }
  { forward. entailer!. }
  apply semax_if_seq. forward_if.
  { exfalso; lia. }
  forward.
  (* next_in = input, next_out = out *)
  sep_apply (c9_open gv vd (Zlib.proof.roundtrip.RTIIface.head_live (init_live sp (su_wbits u)) (h0 u) vg Tsh
               (su_gxp u) (su_gnp u) (su_gcp u)) Nd).
  Intros.
  forward.
  forward.
  (* the inflate loop's invariant: SIFacts.si_head for the header session *)
  assert (SC : sc_gh (scase_of u) = Some (gh_of u)) by (unfold scase_of, sgh; cbn [sc_gh]; rewrite WH; reflexivity).
  pose proof (si_head _ _ _ PF (scase_of u) (su_data u) O src sp (gh_of u) vg Tsh (su_gxp u) (su_gnp u) (su_gcp u)
                I H0 H4 SC) as SH.
  cbv zeta in SH. change (sc_wbits (scase_of u)) with (su_wbits u) in SH.
  change (sc_h0 (scase_of u)) with (h0 u) in SH. rewrite Hiw in SH.
  set (L := Zlib.proof.roundtrip.RTIIface.head_live (init_live sp (su_wbits u)) (h0 u) vg Tsh (su_gxp u) (su_gnp u)
              (su_gcp u)) in *.
  match goal with H : Zlib.proof.roundtrip.RTH8Spec.live_ok8 L |- _ => rename H into LV end.
  destruct (SH LV) as (_ & SW & P0).
  sep_apply (c9_close gv vd ip (su_op u) L LV).
  sep_apply (c9_head9 (init_live sp (su_wbits u)) (h0 u) vg Tsh (su_gxp u) (su_gnp u) (su_gcp u) Wmode
               : Zlib.proof.roundtrip.RTH8Spec.head_mem8 L |-- Zlib.proof.roundtrip.RTH9Spec.head_mem9 L).
  assert (IL : il_ok P u O src ip (mkIL 0 [] false L (c9_z ip (su_op u)))).
  { pose proof Hu as (_ & _ & _ & _ & _ & _ & _ & Po & _).
    unfold il_ok, c9_z; cbn [il_pos il_out il_asked il_L il_z zf_tout zf_ni zf_no].
    rewrite Zlength_nil, !isptr_offset_val_zero by auto.
    pose proof (Zlength_nonneg src).
    split; [exact P0 | split; [exact SW | split; [lia | split; [exists (su_data u); reflexivity | auto]]]]. }
  assert (GA : got_at u vg L) by (unfold got_at; repeat split).
  Exists (mkIL 0 [] false L (c9_z ip (su_op u))).
  cbn [il_pos il_out il_asked il_L il_z].
  rewrite Hiw, <- c9_version.
  unfold Rm.
  entailer!.
Qed.

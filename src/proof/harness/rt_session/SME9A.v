(* Law rt_session (harness/rt_session.c), main's final checks with a header: statements 74 and 75 (asked, next_in), from SMKit.IE_9 to [P76]; SME9B.v proves 76 and 77. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SME9Kit.
Require Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Zlib.proof.harness.rt_stream.USegE Zlib.proof.roundtrip.RTDIface.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* with a header there is no dictionary *)
Lemma head_no_dict (u : setup) : with_head u = true -> with_dict u = false.
Proof.
  unfold with_head, with_dict. intros H. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. rewrite (proj2 (Z.leb_gt _ _) H1). reflexivity.
Qed.

(* statements 74-75 and 76-77 *)
Definition E74_75 : statement :=
  ltac:(let x := eval cbv [E74_77] in
        (match E74_77 with Ssequence a (Ssequence b _) => Ssequence a b | _ => Sskip end) in exact x).
Definition E76_77 : statement :=
  ltac:(let x := eval cbv [E74_77] in
        (match E74_77 with Ssequence _ (Ssequence _ c) => c | _ => Sskip end) in exact x).

Lemma E74_77_split : E74_77 = match E74_75 with Ssequence a b => Ssequence a (Ssequence b E76_77) | s => s end.
Proof. reflexivity. Qed.

(* main's state before statement 76: the decompressor's struct (its next_out read next), out and expected (their
   bytes compared next), and Q9's memory *)
Definition P76 (gv : globals) (vh vg vc va vd : val) (u : setup) (z : zfields) (L : live) (vxf vxl : val)
    : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; zf_no z = offset_val (Zlength (su_data u)) (su_op u);
         Z.land (su_choice u) 2 =? 0 = false -> vxl = Rep.vi (Zlength (su_xf u))]
  (LOCALx (locals9 gv vh vg vc va vd u)
  (SEPx (data_at Tsh t_z (istrm9 gv z (l_sp L)) vd ::
         malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_ep u) ::
         data_at Ews (tarray tuchar (Zlength (su_data u))) (map Rep.vi (su_data u)) (su_ep u) ::
         malloc_token Ews (tarray tuchar (Zlength (su_data u))) (su_op u) ::
         data_at Ews (tarray tuchar (Zlength (su_data u))) (cbytes (Zlength (su_data u)) (su_data u)) (su_op u) ::
         data_at Tsh t_g (gotv u vxf vxl) vg :: data_at Tsh t_g (hvals u) vh :: data_at_ Tsh t_z vc ::
         data_at_ Tsh t_p va :: mem_mgr gv :: TT :: rest78 u))).

Lemma e74_75_ok {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L :
  semax Delta_s (IE_9 gv vh vg vc va vd u O c src ip z L) E74_75
    (overridePost (EX vxf : val, EX vxl : val, P76 gv vh vg vc va vd u z L vxf vxl) POST_s).
Proof.
  unfold IE_9, E74_75.
  destruct POST_s as [r1 r2 r3 r4]. unfold overridePost.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  match goal with H : with_head u = true |- _ => rename H into Hwh end.
  match goal with H : got_at u vg L |- _ => rename H into Hga end.
  match goal with H : g2_hdr_out _ _ _ _ |- _ => rename H into Hho end.
  match goal with H : IR.i_head _ = true |- _ => rename H into Hih end.
  match goal with H : SIFacts.src_ok _ _ |- _ => destruct H as (Hso & Hsub & Hsb) end.
  pose proof (head_no_dict u Hwh) as Hwd.
  pose proof (Zlength_nonneg O) as LO. pose proof (Zlength_nonneg (su_data u)) as LD.
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & Ld & Bd & _ & _ & _ & _ &
    Px & Pn & Pc & Pe & Po & Pgx & Pgn & Pgc).
  unfold d_locals, c_locals, lvs, lv_locals. rewrite Hwd, Hwh. cbn [app andb Z.b2z].
  unfold UDFacts.max_size in Hso, Ld.
  sep_apply (istream8_view gv vd z L).
  sep_apply (got_view9 u L vg ltac:(assumption) Hho Hih Hga). Intros vxf vxl.
  sep_apply (cstream_back9 gv vc (ghp vh u) c).
  unfold hobj. sep_apply (hobjs_view9 u).
  unfold oobj, dobj, eobj, bobj, iobj, istrm9.
  match goal with H : zf_ni z = _ |- _ => rewrite H end.
  match goal with H : zf_no z = _ |- _ => rewrite H end.
  Intros.
  freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 19; 22; 25; 26; 27] FR0.
  (* statement 74: asked (0: no dictionary with a header) against with_dict && window_bits > 0 *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'85 (Vint Int.zero) :: Q) (SEPx R))) end.
  { exfalso. auto. }
  { forward. entailer!. }
  forward_call (Int.repr 1).
  (* statement 75: next_in == input + compressed_len *)
  forward.
  forward_call (Int.repr 1).
  { rewrite USegE.add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans; [ | apply (test_eq_self9 TT ip (Zlength O) (Zlength src) (map Rep.vi src))]; [cancel | | auto].
    lia. }
  { entailer!. rewrite USegE.add_ptr_long_tuchar by (auto; rep_lia). destruct ip; try contradiction.
    simpl. unfold sem_cmp_pp. simpl. rewrite peq_true, Ptrofs.eq_true. reflexivity. }
  Exists vxf vxl. unfold P76, locals9, lvs, lv_locals, c_locals, d_locals, rest78, istrm9. thaw FR0.
  rewrite Hwd, Hwh.
  match goal with H : zf_ni z = _ |- _ => rewrite H end.
  match goal with H : zf_no z = _ |- _ => rewrite H end.
  cbn [app]. entailer!.
Qed.

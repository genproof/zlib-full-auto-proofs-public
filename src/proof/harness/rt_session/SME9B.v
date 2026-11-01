(* Law rt_session (harness/rt_session.c), main's final checks with a header: statements 76 and 77 (next_out and the bytes, the !with_head test), from SME9A.P76 to SME9Kit.Q9; with SME9A.v, statements 74-77. *)
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
Require Import Zlib.proof.harness.rt_session.SME9A.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma e76_77_ok {Espec : OracleKind} gv vh vg vc va vd u z L vxf vxl :
  semax Delta_s (P76 gv vh vg vc va vd u z L vxf vxl) E76_77
    (overridePost (EX vxf' : val, EX vxl' : val, Q9 gv vh vg vc va vd u vxf' vxl' [] (rest78 u)) POST_s).
Proof.
  unfold P76, E76_77.
  destruct POST_s as [r1 r2 r3 r4]. unfold overridePost.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  match goal with H : with_head u = true |- _ => rename H into Hwh end.
  pose proof (head_no_dict u Hwh) as Hwd.
  pose proof (Zlength_nonneg (su_data u)) as LD.
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & Ld & Bd & _ & _ & _ & _ &
    Px & Pn & Pc & Pe & Po & Pgx & Pgn & Pgc).
  unfold UDFacts.max_size in Ld.
  unfold locals9, d_locals, c_locals, lvs, lv_locals, rest78, istrm9. rewrite Hwd, Hwh. cbn [app andb Z.b2z].
  match goal with H : zf_no z = _ |- _ => rewrite H end.
  freeze [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16] FR0.
  (* statement 76: next_out == out + data_len and out's bytes against expected's *)
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'86 (Vint Int.one) :: Q) (SEPx R))) end.
  { rewrite USegE.add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans;
      [ | apply (test_eq_self9 TT (su_op u) (Zlength (su_data u)) (Zlength (su_data u))
                   (cbytes (Zlength (su_data u)) (su_data u)))];
      [cancel | | auto].
    lia. }
  { rewrite <- (bytes_a9 Ews (Zlength (su_data u)) (cbytes (Zlength (su_data u)) (su_data u)) (su_op u)).
    rewrite <- (bytes_a9 Ews (Zlength (su_data u)) (map Rep.vi (su_data u)) (su_ep u)).
    forward_call (su_op u, Ews, su_op u, 0, Zlength (su_data u), cbytes (Zlength (su_data u)) (su_data u), su_data u,
                  su_ep u, Ews, su_ep u, 0, Zlength (su_data u), map Rep.vi (su_data u), su_data u,
                  Zlength (su_data u)).
    { split; [apply USegE.cbuf_ok_data | apply USegE.cbuf_ok_data']; auto. }
    rewrite (bytes_a9 Ews (Zlength (su_data u)) (cbytes (Zlength (su_data u)) (su_data u)) (su_op u)).
    rewrite (bytes_a9 Ews (Zlength (su_data u)) (map Rep.vi (su_data u)) (su_ep u)).
    destruct (list_eq_dec Z.eq_dec (su_data u) (su_data u)) as [_ | NE]; [ | congruence].
    forward. entailer!. }
  { exfalso. match goal with Hn : offset_val _ _ <> _ |- _ =>
      rewrite USegE.add_ptr_long_tuchar in Hn by (auto; rep_lia); congruence end. }
  forward_call (Int.repr 1).
  (* statement 77: with a header, !with_head is false *)
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  forward.
  Exists vxf vxl. unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals, rest78. thaw FR0.
  rewrite Hwd, Hwh.
  match goal with |- context [data_at Tsh t_z ?v vd] => sep_apply (data_at_data_at_ Tsh t_z v vd) end.
  cbn [app]. entailer!.
Qed.

(* statements 74-77 *)
Lemma e74_77_ok {Espec : OracleKind} gv vh vg vc va vd u O c src ip z L :
  semax Delta_s (IE_9 gv vh vg vc va vd u O c src ip z L) E74_77
    (overridePost (EX vxf : val, EX vxl : val, Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) POST_s).
Proof.
  rewrite E74_77_split. cbv beta iota delta [E74_75].
  apply seq_assoc.
  eapply semax_seq; [ apply e74_75_ok | ].
  apply extract_exists_pre; intro vxf. apply extract_exists_pre; intro vxl.
  apply e76_77_ok.
Qed.

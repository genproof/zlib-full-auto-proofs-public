(* Law rt_session (harness/rt_session.c), main's header checks: statement 80, same_field(choice & 2, got.extra, extra_copy, extra_len). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SME9Kit.
Require Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma e80_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) E80
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] (rest81 u)) POST_s).
Proof.
  unfold E80.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & _ & _ & _ & _ & _ & _ &
    Px & Pn & Pc & _ & _ & Pgx & Pgn & Pgc).
  pose proof (gq_pn9 u 2 _ Pgx).
  unfold gotv, rest78, hx9.
  freeze [1; 2; 3; 4; 5; 6; 8; 9; 11; 12] FR0.
  forward.
  sep_apply (sf_pre9 u 2 (su_gxp u) (su_xcp u) (Zlength (su_xf u)) (su_xf u)). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (su_choice u) 2, gq u 2 (su_gxp u), su_xcp u, Zlength (su_xf u), Ews, Ews, su_xf u, su_xf u).
  { split; [ pose proof (E9K7.land_range (su_choice u) 2 Rch ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply E9K7.is_bytes_r; exact Bx ]. }
  rewrite (sf_one9 u 2 (su_gxp u) (su_xf u) Pgx).
  forward_call (Int.repr 1).
  destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv, rest81. cbn [app]. entailer!.
Qed.

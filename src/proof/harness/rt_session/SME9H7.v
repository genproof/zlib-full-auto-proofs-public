(* Law rt_session (harness/rt_session.c), main's header checks: statement 82, same_field(choice & 4, got.name, name_copy, name_len + 1). *)
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

Lemma e82_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest81 u)) E82
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] (rest83 u)) POST_s).
Proof.
  unfold E82.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & _ & _ & _ & _ & _ & _ &
    Px & Pn & Pc & _ & _ & Pgx & Pgn & Pgc).
  pose proof (gq_pn9 u 4 _ Pgn).
  assert (Ln1 : Zlength (su_nm u ++ [0]) = Zlength (su_nm u) + 1) by (rewrite Zlength_app; reflexivity).
  unfold gotv, rest81, hn9.
  freeze [1; 2; 3; 4; 5; 6; 8; 10] FR0.
  forward.
  sep_apply (sf_pre9 u 4 (su_gnp u) (su_ncp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0])). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (su_choice u) 4, gq u 4 (su_gnp u), su_ncp u, Zlength (su_nm u) + 1, Ews, Ews,
                su_nm u ++ [0], su_nm u ++ [0]).
  { split; [ pose proof (E9K7.land_range (su_choice u) 4 Rch ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply E9K7.is_bytes_nz; exact Bn ]. }
  rewrite (sf_one9 u 4 (su_gnp u) (su_nm u ++ [0]) Pgn).
  forward_call (Int.repr 1).
  destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv, rest83. cbn [app]. entailer!.
Qed.

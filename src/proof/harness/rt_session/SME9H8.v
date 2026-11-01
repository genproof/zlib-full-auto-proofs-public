(* Law rt_session (harness/rt_session.c), main's header checks: statement 83, same_field(choice & 8, got.comment, comment_copy, comment_len + 1), and the return (statement 84). *)
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

Lemma e83_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest83 u)) E83
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] []) POST_s).
Proof.
  unfold E83.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & _ & _ & _ & _ & _ & _ &
    Px & Pn & Pc & _ & _ & Pgx & Pgn & Pgc).
  pose proof (gq_pn9 u 8 _ Pgc).
  assert (Lc1 : Zlength (su_cm u ++ [0]) = Zlength (su_cm u) + 1) by (rewrite Zlength_app; reflexivity).
  unfold gotv, rest83, hc9.
  freeze [1; 2; 3; 4; 5; 6] FR0.
  forward.
  sep_apply (sf_pre9 u 8 (su_gcp u) (su_ccp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0])). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (su_choice u) 8, gq u 8 (su_gcp u), su_ccp u, Zlength (su_cm u) + 1, Ews, Ews,
                su_cm u ++ [0], su_cm u ++ [0]).
  { split; [ pose proof (E9K7.land_range (su_choice u) 8 Rch ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply E9K7.is_bytes_nz; exact Bc ]. }
  rewrite (sf_one9 u 8 (su_gcp u) (su_cm u ++ [0]) Pgc).
  forward_call (Int.repr 1).
  destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv. cbn [app]. entailer!.
Qed.

(* return 0: main's five locals are given back (head and got from their structs), the rest goes to TT *)
Lemma e84_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] []) E84 POST_s.
Proof.
  unfold E84, POST_s.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  forward. Exists (Int.repr 0). apply andp_right; [ apply prop_right; reflexivity | ].
  do 2 match goal with |- context [data_at Tsh t_g ?v ?p] => sep_apply (data_at_data_at_ Tsh t_g v p) end.
  cancel.
Qed.

(* Law rt_session (harness/rt_session.c), main's header checks: statement 81, !(choice & 2) || got.extra_len == extra_len. *)
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

Lemma e81_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest81 u)) E81
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] (rest81 u)) POST_s).
Proof.
  unfold E81.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof (su_ok_e9 u ltac:(assumption)) as (Rch & Lx & Bx & Ln & Bn & Lc & Bc & _ & _ & _ & _ & _ & _ &
    Px & Pn & Pc & _ & _ & Pgx & Pgn & Pgc).
  unfold gotv, rest81.
  freeze [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] FR.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'92 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { assert (E : Z.land (su_choice u) 2 =? 0 = false).
    { match goal with Hc : Int.and _ _ <> Int.zero |- _ => rewrite E9K7.land_repr in Hc by lia end.
      destruct (Z.eqb_spec (Z.land (su_choice u) 2) 0) as [E0 | ]; [ | reflexivity ].
      exfalso. rewrite E0 in *. contradiction. }
    match goal with Hx : _ = false -> vxl = _ |- _ => rewrite (Hx E) end.
    forward.
    forward.
    match goal with Hx : _ = false -> vxl = _ |- _ => rewrite (Hx E) end.
    rewrite Int.unsigned_repr by rep_lia. destruct (zeq (Zlength (su_xf u)) (Zlength (su_xf u))); [ | congruence ].
    freeze FR2 := (data_at Tsh t_g _ vg). entailer!. thaw FR2. cancel. }
  forward_call (Int.repr 1).
  destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR.
  unfold gotv, rest81. cbn [app]. entailer!.
Qed.

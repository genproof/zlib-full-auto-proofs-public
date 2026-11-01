(* Law rt_gzip_header, main's body, segment 7: the first part of statement 41 (G2MS7Kit.S41), the test
   got.os == (os & 255) && got.time == time of gp_assert(got.os == (os & 255) && got.time == time) (os and time
   are main's locals); its gp_assert is G2MS7B.s41b_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* statement 41 cut in two: its test and its gp_assert *)
Definition S41a : statement :=
  ltac:(let x := eval cbv [S41] in (match S41 with Ssequence a _ => a | _ => Sskip end) in exact x).
Definition S41b : statement :=
  ltac:(let x := eval cbv [S41] in (match S41 with Ssequence _ b => b | _ => Sskip end) in exact x).

Lemma S41_split : S41 = Ssequence S41a S41b.
Proof. reflexivity. Qed.

Lemma s41a_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) S41a
    (overridePost (Q7x gv vh vg vc vd vr g Fr vxf vxl [temp _t'46 (Vint Int.one)] (rest40 g)) POST_m).
Proof.
  unfold Q7, Q7x, S41a, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  unfold gotv, rest40.
  freeze FR0 := (data_at Tsh t_g _ vh) Fr (mem_mgr gv) (R gv) (gfield g 1 _ _ _) (gfield g 2 _ _ _)
    (gfield g 4 _ _ _) (hx7 g) (hn7 g) (hc7 g).
  forward.
  forward_if.
  { forward. forward.
    destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR0.
    unfold gotv, rest40. cbn [app]. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  { exfalso. match goal with H : Int.repr (Z.land _ 255) <> _ |- _ => apply H end.
    apply Int.same_if_eq, os_eq. }
Qed.

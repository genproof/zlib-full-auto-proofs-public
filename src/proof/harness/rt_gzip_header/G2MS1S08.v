(* Law rt_gzip_header, main's body, segment 1: statements 8-10, extra = alloc_any_bytes(extra_len),
   name = any_string(name_len), comment = any_string(comment_len). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma g1s08_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh :
  semax Delta_m (Q1 gv vh vg vc vd vr xl nl cl pr ut utm uo uh) (Ssequence (Ssequence S8 S9) S10)
    (overridePost (EX xp : val, EX xf : list Z, EX np : val, EX nm : list Z, EX cp : val, EX cm : list Z, QO gv vh
        vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) POST_m).
Proof.
  unfold Q1, Qs, fs1, dr_temps, sc_temps, lv_locals, S8, S9, S10. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward_call (xl, gv). Intros vret. destruct vret as [xp xf]. cbn [fst snd] in *.
  forward_call (nl, gv). Intros vret. destruct vret as [np nm]. cbn [fst snd] in *.
  forward_call (cl, gv). Intros vret. destruct vret as [cp cm]. cbn [fst snd] in *.
  forward.
  Exists xp xf np nm cp cm.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QO, Qs, fs2, objs3, dr_temps, sc_temps, ob_temps, lv_locals, dr_ok, u32, obj0, nzbytes.
  cbn [app].
  entailer!.
  split; (eapply Forall_impl; [ | eassumption]; cbv beta; intros; rep_lia).
Qed.

(* Law rt_gzip_header, main's body, segment 1: statements 0-7, the draws of extra_len, name_len, comment_len,
   present and of the locals text, time, os and hcrc. *)
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

Lemma g1s00_ok {Espec : OracleKind} gv vh vg vc vd vr :
  semax Delta_m (PRE0 gv vh vg vc vd vr) (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
      (Ssequence S0 S1) S2) S3) S4) S5) S6) S7)
    (overridePost (EX xl : Z, EX nl : Z, EX cl : Z, EX pr : Z, EX ut : Z, EX utm : Z, EX uo : Z, EX uh : Z, Q1 gv vh
        vg vc vd vr xl nl cl pr ut utm uo uh) POST_m).
Proof.
  unfold PRE0, lv_locals, S0, S1, S2, S3, S4, S5, S6, S7. rewrite !data_at_g.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  forward_call 65535. Intros xl.
  forward_call 4294967294. Intros nl.
  forward_call 4294967294. Intros cl.
  forward_call. Intros pr.
  forward_call. Intros ut.
  rewrite <- !seq_assoc. forward_call. Intros utm. forward.
  forward_call. Intros uo.
  forward_call. Intros uh. forward.
  Exists xl nl cl pr ut utm uo uh.
  unfold Q1, Qs, fs1, sc_temps, dr_temps, dr_ok, u32, lv_locals. cbn [app].
  rewrite Int.unsigned_repr by rep_lia.
  entailer!.
Qed.

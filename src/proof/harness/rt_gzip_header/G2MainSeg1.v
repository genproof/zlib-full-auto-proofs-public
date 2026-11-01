(* Law rt_gzip_header, main's body, segment 1 (G2MainKit.seg1_stmt): statements 0-33, the draws, the test of the
   three objects, their copies, the stores into head and got, the allocations and the NULL test of the copies and of
   got's buffers.

   The statements are proved one store or load at a time between the states of G2MS1Kit.v (files G2MS1S00.v ..
   G2MS1Ret.v, listed in G2MS1Kit.v's first comment), as the stores into head and got cost seconds each; statement 33
   one operand of its condition at a time, each operand by the cases of the previous operand's value and of the
   pointer it tests. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1Kit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S00.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S08.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S11a.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S11b.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S11c.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S12.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S15.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S16.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S17.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S18.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S19.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S20.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S21.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S22.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S23.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S27.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S28.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S29.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S30.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S31.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S32.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O27a.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O27b.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O27c.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O28.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1OT1.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1OT2.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O29n.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O29p.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O30n.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O30p.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O31n.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1O31p.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1Ret.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* a test's value, without replacing it in the goal (the operand lemmas are stated with it) *)
Lemma bool_cases (b : bool) : b = true \/ b = false.
Proof. destruct b; auto. Qed.

Section Operands.
Context {Espec : OracleKind} (gv : globals) (vh vg vc vd vr : val) (g : gsetup).

(* the operands of statement 33, all cases together *)
Lemma g1op27 :
  semax Delta_m (NS gv vh vg vc vd vr g []) I27
    (overridePost (NS gv vh vg vc vd vr g [temp _t'27 (vb (f27 g))]) POST_m).
Proof.
  destruct (eq_dec (g_xcp g) nullval) as [Hx | Hx]; [now apply g1o27_null |].
  destruct (eq_dec (g_ncp g) nullval) as [Hn | Hn]; [now apply g1o27_pn | now apply g1o27_pp].
Qed.

Lemma g1op28 :
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'27 (vb (f27 g))]) I28
    (overridePost (NS gv vh vg vc vd vr g [temp _t'28 (vb (f28 g))]) POST_m).
Proof. destruct (bool_cases (f27 g)) as [E | E]; [now apply g1t28_ok | now apply g1f28_ok]. Qed.

Lemma g1op29 :
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'28 (vb (f28 g))]) I29
    (overridePost (NS gv vh vg vc vd vr g [temp _t'29 (vb (f29 g))]) POST_m).
Proof.
  destruct (bool_cases (f28 g)) as [E | E]; [now apply g1t29_ok |].
  destruct (eq_dec (g_gxp g) nullval); [now apply g1f29n_ok | now apply g1f29p_ok].
Qed.

Lemma g1op30 :
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'29 (vb (f29 g))]) I30
    (overridePost (NS gv vh vg vc vd vr g [temp _t'30 (vb (f30 g))]) POST_m).
Proof.
  destruct (bool_cases (f29 g)) as [E | E]; [now apply g1t30_ok |].
  destruct (eq_dec (g_gnp g) nullval); [now apply g1f30n_ok | now apply g1f30p_ok].
Qed.

Lemma g1op31 :
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'30 (vb (f30 g))]) I31
    (overridePost (NS gv vh vg vc vd vr g [temp _t'31 (vb (f31 g))]) POST_m).
Proof.
  destruct (bool_cases (f30 g)) as [E | E]; [now apply g1t31_ok |].
  destruct (eq_dec (g_gcp g) nullval); [now apply g1f31n_ok | now apply g1f31p_ok].
Qed.
End Operands.

(* one statement (or a group, nested to the left) from a state to the next *)
Ltac g1_step L :=
  eapply semax_seq; [ rewrite overridePost_overridePost; apply L | ];
  repeat (apply extract_exists_pre; intro).

Lemma g2seg1_ok : seg1_stmt.
Proof.
  intros Espec gv vh vg vc vd vr. rewrite seg1_split.
  do 7 apply seq_left. g1_step g1s00_ok.    (* 0-7 *)
  do 2 apply seq_left. g1_step g1s08_ok.    (* 8-10 *)
  g1_step g1s11_ok.                         (* 11 *)
  do 2 apply seq_left. g1_step g1s12_ok.    (* 12-14 *)
  g1_step g1s15_ok.                         (* 15 *)
  g1_step g1s16_ok.                         (* 16 *)
  g1_step g1s17_ok.                         (* 17 *)
  g1_step g1s18_ok.                         (* 18 *)
  g1_step g1s19_ok.                         (* 19 *)
  g1_step g1s20_ok.                         (* 20 *)
  g1_step g1s21_ok.                         (* 21 *)
  g1_step g1s22_ok.                         (* 22 *)
  do 3 apply seq_left. g1_step g1s23_ok.    (* 23-26 *)
  g1_step g1s27_ok.                         (* 27 *)
  g1_step g1s28_ok.                         (* 28 *)
  g1_step g1s29_ok.                         (* 29 *)
  g1_step g1s30_ok.                         (* 30 *)
  g1_step g1s31_ok.                         (* 31 *)
  g1_step g1s32_ok.                         (* 32 *)
  (* statement 33 *)
  rewrite S33_split.
  eapply semax_seq; [ | apply g1ret_ok ].
  eapply semax_seq; [ | rewrite overridePost_overridePost; apply g1op31 ].
  eapply semax_seq; [ | rewrite !overridePost_overridePost; apply g1op30 ].
  eapply semax_seq; [ | rewrite !overridePost_overridePost; apply g1op29 ].
  eapply semax_seq; [ | rewrite !overridePost_overridePost; apply g1op28 ].
  rewrite !overridePost_overridePost. apply g1op27.
Qed.

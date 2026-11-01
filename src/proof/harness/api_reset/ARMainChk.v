(* Law api_reset, main: the asserts of phase 1 (ARMainKit.seg_chk): both calls returned the same code, left
   the same avail_in and avail_out, wrote the same bytes, and leave the same totals, msg, data_type and (for
   windowBits >= 0) adler.  The sixth assert is proved here, the others in ARMainChkA.v to ARMainChkD.v; each
   keeps ARMainChkA.chk_pre, the assertion mid1_at with both structs z_stream opened. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainChkA.
Require Import Zlib.proof.harness.api_reset.ARMainChkB.
Require Import Zlib.proof.harness.api_reset.ARMainChkC.
Require Import Zlib.proof.harness.api_reset.ARMainChkD.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

(* gp_assert(window_bits < 0 || used.adler == fresh.adler): for windowBits >= 0 neither stream is raw, so
   strm->adler holds the model's adler on both, equal by mid1_facts *)
Lemma chk_c6 : chk_part seg_c6.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  pose proof MF as ((_ & _ & Hw & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    Eadl & _).
  unfold seg_c6, chk_pre at 1, chk_tup. Intros. abbreviate_semax.
  destruct (Z.ltb_spec w 0) as [Hn | Hn]; unfold adler_v.
  - apply semax_if_seq. forward_if.
    + forward. forward_call (Int.repr 1).
      unfold chk_pre, chk_tup, adler_v. rewrite (proj2 (Z.ltb_lt w 0) Hn). entailer!.
    + exfalso. lia.
  - apply semax_if_seq. forward_if.
    + exfalso. lia.
    + forward. forward. forward. forward_call (Int.repr 1).
      { entailer!. rewrite (Eadl Hn), Int64.eq_true. reflexivity. }
      unfold chk_pre, chk_tup, adler_v. rewrite (proj2 (Z.ltb_ge w 0) Hn). entailer!.
Qed.

Lemma chk_proof : chk_stmt.
Proof.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  assert (A: chk_part seg_chk).
  { rewrite seg_chk_eq.
    apply chk_part_seq; [exact chk_c1 | ]. apply chk_part_seq; [exact chk_c2 | ].
    apply chk_part_seq; [exact chk_c3 | ]. apply chk_part_seq; [exact chk_c4 | ].
    apply chk_part_seq; [exact chk_c5 | exact chk_c6]. }
  eapply semax_pre; [apply (chk_pre_of J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF) | ].
  eapply semax_post'; [apply (chk_post_of J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF) | ].
  exact (A Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF).
Qed.

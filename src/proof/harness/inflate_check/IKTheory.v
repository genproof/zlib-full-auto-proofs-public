(* Law inflate_check: the pure theory (IKFacts.v's interface), from the parts IKBits.v, IKTh*.v, IKTheoryCall.v
   and the intra-call invariant of the model (inflate_codes' ICStepMwf.ic_stepf2_mwf3). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Import Zlib.proof.harness.inflate_check.IKBits Zlib.proof.harness.inflate_check.IKThHead
               Zlib.proof.harness.inflate_check.IKThHdr Zlib.proof.harness.inflate_check.IKThDict
               Zlib.proof.harness.inflate_check.IKThBlock Zlib.proof.harness.inflate_check.IKThFast
               Zlib.proof.harness.inflate_check.IKThDec Zlib.proof.harness.inflate_check.IKThTab
               Zlib.proof.harness.inflate_check.IKTheoryCall.
Require Zlib.proof.harness.inflate_codes.TheoryRun Zlib.proof.harness.uncompress_any.UAStepMwf.

Lemma ik_all : groupx_okb (fun _ => True).
Proof.
  pose proof ik_kit_proof as K.
  pose proof Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 as SM.
  assert (DE: groupx_ok decode_mode) by exact (ikx_dec K (ikx_fast K)).
  assert (TA: groupx_ok md_tab) by exact (ikx_tab K SM DE).
  intros wrap src pos out a0 inp aout flush m C KC KX W L _ OB.
  pose proof (sw_mode _ (mw_s _ (mwf3_mwf _ W))) as R.
  destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_mode_groups (m_mode m) R)
    as [G|[G|[G|[G|[G|[G|G]]]]]].
  - exact ((ikx_head K) _ _ _ _ _ _ _ _ _ C KC KX W L G).
  - exact ((ikx_hdr K) _ _ _ _ _ _ _ _ _ C KC KX W L G).
  - exact ((ikx_dict K) _ _ _ _ _ _ _ _ _ C KC KX W L G).
  - exact ((ikx_block K) _ _ _ _ _ _ _ _ _ C KC KX W L G OB).
  - exact (DE _ _ _ _ _ _ _ _ _ C KC KX W L G).
  - exact (TA _ _ _ _ _ _ _ _ _ C KC KX W L G).
  - exfalso. exact (kc_sync _ _ _ _ _ _ KC G).
Qed.

Lemma ik_theory : ik_theory_stmt.
Proof. exact (ikx_callb ik_kit_proof ik_all). Qed.

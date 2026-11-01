(* The two round-trip laws (compress_roundtrip, deflate_roundtrip), from the body obligations of the inflate
   area (inflate_lib5_stmt, uncompr_bodies5_stmt), the decode theory's parts (rfc1951 Decode.decode_parts) and
   the obligations of the deflate area (trees_bodies_ok, deflate_bodies_ok9 (v9 init/reset specs), the huffman
   lemmas), which src/contracts/suite.v discharges with the areas' proofs. *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_compress_roundtrip Zlib.contracts.x_deflate_roundtrip.
Require Zlib.proof.inflate_api.LibStmt5 Zlib.proof.uncompr.UBodies5 Zlib.proof.rfc1951.Decode.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Require Zlib.proof.deflate.LawTheory.
Require Zlib.proof.roundtrip.RTDTheory.
Require Zlib.proof.roundtrip.RTUTheory.
Require Zlib.proof.roundtrip.RTCTheory.
Require Zlib.proof.roundtrip.RTBTheory.
Require Zlib.proof.roundtrip.RTXTheory.
Require Zlib.proof.roundtrip.RTCBodies.
Require Zlib.proof.roundtrip.RTCLaw.
Require Zlib.proof.roundtrip.RTRLaw6.
Require Zlib.proof.roundtrip.RTHTheory.
Require Zlib.proof.roundtrip.RTHIface.

Theorem roundtrip_laws :
  Zlib.proof.inflate_api.LibStmt5.inflate_lib5_stmt ->
  Zlib.proof.uncompr.UBodies5.uncompr_bodies5_stmt ->
  Zlib.proof.rfc1951.Decode.decode_parts ->
  Zlib.proof.deflate.Obligations.trees_bodies_ok ->
  Zlib.proof.deflate.Obligations9.deflate_bodies_ok9 ->
  Zlib.proof.huffman.Overlay.overlay_statement ->
  Zlib.proof.huffman.BlockBound.block_bound_statement ->
  harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog /\
  harness_safe Zlib.contracts.x_deflate_roundtrip.whole_prog.
Proof.
  intros HI HU HD HT HB Hov Hbb.
  destruct (Zlib.proof.deflate.LawTheory.law_theory Hov Hbb) as [[I [Iend AF]] _].
  destruct (Zlib.proof.roundtrip.RTDTheory.rt_kfacts Hov) as [K KF].
  destruct (Zlib.proof.roundtrip.RTBTheory.rt_b_facts Hov Hbb) as [HIn HBo].
  pose proof (Zlib.proof.roundtrip.RTCTheory.rt_c2_fact K KF HIn HBo) as C2.
  pose proof (Zlib.proof.roundtrip.RTUTheory.rt_ufacts HD) as UF.
  destruct (Zlib.proof.roundtrip.RTXTheory.rt_ik_facts I Iend K AF KF) as [AF' RX].
  assert (DE : Zlib.proof.deflate.Obligations.ob_dstream_to_end).
  { unfold Zlib.proof.deflate.Obligations9.deflate_bodies_ok9 in HB. tauto. }
  pose proof (Zlib.proof.roundtrip.RTCBodies.rt_compress_bodies DE) as CB.
  split.
  - exact (Zlib.proof.roundtrip.RTCLaw.rt_compress_law HI HU HT HB CB C2 UF).
  - apply (Zlib.proof.roundtrip.RTRLaw6.rt_deflate_law6 HI (Zlib.proof.roundtrip.RTHTheory.rt_head6 HI) HT HB);
      [ | exact (Zlib.proof.roundtrip.RTHIface.rt_ifacts6 HD) ].
    exists (Zlib.proof.roundtrip.RTXFacts.ik I K), Iend. split; assumption.
Qed.

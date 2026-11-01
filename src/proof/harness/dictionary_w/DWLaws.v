(* The laws rt_dictionary and api_dict_id for data of any length and a dictionary of up to 2^32 - 1 bytes (the
   harnesses compress all of the data in clip() pieces into deflateBound_z bytes; api_dict_id checks the first
   inflate() call: Z_NEED_DICT with the dictionary's Adler-32; rt_dictionary then sets the dictionary and
   inflates the rest with Z_FINISH in clip() pieces).  From the deflate side of the round trips
   (RTK7.rt_k7_stmt), the wide deflateBound accounting (LawFactsW2.bound_w_big_stmt), the wide decode theory
   (Decode7) and inflate.c's bodies for SpecW's specifications (SpecWLib.specw_lib_stmt). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_dictionary.
Require Zlib.contracts.api_dict_id.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWDTheory.
Require Import Zlib.proof.harness.dictionary_w.DWITheory.
Require Import Zlib.proof.harness.dictionary_w.DWMains.
Require Import Zlib.proof.harness.dictionary_w.DWAsm.

Lemma dictionary_w_laws : laws_common_ok -> rt_k7_stmt -> decode_init7_stmt -> decode_call7_stmt ->
  Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt -> Zlib.proof.deflate.LawFactsW2.bound_w_big_stmt ->
  harness_safe Zlib.contracts.rt_dictionary.whole_prog /\ harness_safe Zlib.contracts.api_dict_id.whole_prog.
Proof.
  intros L K DI DC SW BW.
  exact (dict_asm L SW (proj1 dict_mains) (proj2 dict_mains) (dict_dtheory K BW) (dict_itheory DI DC)).
Qed.

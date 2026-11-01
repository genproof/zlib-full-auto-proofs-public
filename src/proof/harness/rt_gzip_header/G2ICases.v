(* Law rt_gzip_header on the round-2 harness, inflate side: the header cases HEAD .. HCRC of inflate() for a gzip
   header split over calls of any size (G2IDefs.case_ok2), adapted from law inflate_header's IHTCase*.v.  The cases
   are proved in G2ICaseHF.v (HEAD, FLAGS), G2ICaseTOE.v (TIME, OS, EXLEN), G2ICaseEx.v (EXTRA), G2ICaseNC.v (NAME,
   COMMENT) and G2ICaseHc.v (HCRC), each assuming the case it falls through into; the kit is law inflate_header's
   (IHTKit*.v), whose facts do not depend on the layout of the input. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Import Zlib.proof.harness.inflate_header.IHTKitNb.
Require Import Zlib.proof.harness.inflate_header.IHTKitStr.
Require Import Zlib.proof.harness.inflate_header.IHTKitMisc.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseHF.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseTOE.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseEx.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseNC.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseHc.
Import ListNotations.
Local Open Scope Z_scope.

(* the facts about bytes, bit buffers and the model's helpers the cases use *)
Lemma g2_kit_proof : g2_kit.
Proof.
  constructor; [exact ihm_bits | exact ih_nb_proof | exact ihs_zstr | exact ihs_put | exact ihm_crc
               | exact ihm_in].
Qed.

Lemma g2_cases : g2_cases_stmt.
Proof.
  pose proof g2_kit_proof as KIT.
  pose proof (g2c_hcrc KIT) as CH.
  pose proof (proj2 g2c_nc KIT CH) as CC.
  pose proof (proj1 g2c_nc KIT CC) as CN.
  pose proof (g2c_extra KIT CN) as CE.
  pose proof (g2c_exlen KIT CE) as CX.
  pose proof (g2c_os KIT CX) as CO.
  pose proof (g2c_time KIT CO) as CT.
  pose proof (g2c_flags KIT CT) as CF.
  refine (conj _ (conj CF (conj CT (conj CO (conj CX (conj CE (conj CN (conj CC CH)))))))).
  intros g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  apply (g2c_head_nz KIT); auto.
  pose proof (jc2_wb _ _ _ _ (km2_jc _ _ _ _ _ _ _ _ _ K)). lia.
Qed.

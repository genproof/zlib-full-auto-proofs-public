(* The bodies of the generated allocator-generic port of deflate.c (src/proof/za/deflate/, generator
   docs/port-za/port.py with docs/port-za/cfg_deflate.py) against their specifications, for every
   caller-supplied allocator. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.za.deflate.Body_leaf.
Require Import Zlib.proof.za.deflate.Body_window.
Require Import Zlib.proof.za.deflate.Body_stored.
Require Import Zlib.proof.za.deflate.Body_compress.
Require Import Zlib.proof.za.deflate.MainDeflate.
Require Import Zlib.proof.za.deflate.Api_resetkeep9.
Require Import Zlib.proof.za.deflate.Api_reset9.
Require Import Zlib.proof.za.deflate.Api_toend.

Lemma za_deflate_bodies : za_deflate_bodies_stmt.
Proof.
  intros ZA.
  destruct (@deflate_leaf_za ZA) as (Hrb & _ & Hfp & _ & _ & Hsc).
  destruct (@deflate_window_za ZA) as (Hfw & _).
  destruct (@deflate_compress_za ZA) as (Hfa & Hsl & Hrl & Hhf).
  exact (conj Hrb (conj Hfp (conj Hfw (conj (@deflate_stored_body_za ZA) (conj Hfa (conj Hsl (conj Hrl
    (conj Hhf (conj Hsc (conj (@body_deflateResetKeep9_za ZA) (conj (@body_deflateReset9_za ZA)
    (conj (@body_deflate_za ZA) (@dstream_to_end_za ZA))))))))))))).
Qed.

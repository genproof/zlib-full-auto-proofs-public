(* Law deflate_roundtrip, main (kit: RTRMKit.v): the inflate interface RTIIface.ifacts' if_zdict allows the
   first inflate() call on a zlib stream with a dictionary to return Z_MEM_ERROR, while the harness asserts
   r == Z_NEED_DICT there.  inflate returns Z_NEED_DICT from state DICT directly, before any window allocation:
   RTIZDictFirst.rtz_first gives r_ret = Z_NEED_DICT for every run2 result (as RTZNTheory.rt_zd_nomem). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTRMKit.
Require Import Zlib.proof.roundtrip.RTIZDictDefs Zlib.proof.roundtrip.RTIZDictKit Zlib.proof.roundtrip.RTIZDictFirst.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rm_zd_nomem : zd_nomem.
Proof.
  intros wb dict D O sp z res DF Hne _ _ _ _ ZC RUN.
  destruct DF as (Hwb & bs & WF & Hdata & DW).
  destruct DW as (_ & flg & FL & HOeq).
  assert (EM : negb (match dict with [] => true | _ => false end) = true) by (destruct dict; [congruence|reflexivity]).
  assert (EB : match dict with [] => [] | _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 end =
               be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4) by (destruct dict; [congruence|reflexivity]).
  rewrite EM in FL. rewrite EB in HOeq. clear EM EB.
  set (id := Zlib.proof.adler32.Model.ref_adler32 1 dict) in *.
  set (T := deflate_bytes bs ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4) in *.
  destruct ZC as (ZF & _ & _ & _).
  pose proof (rtz_first Z_FINISH wb flg id T z sp res Hwb FL (rtzk_adler_range dict) ZF) as R1.
  rewrite HOeq in RUN. specialize (R1 RUN).
  destruct R1 as (R1 & _). rewrite R1. unfold Z_NEED_DICT, Z_MEM_ERROR. lia.
Qed.

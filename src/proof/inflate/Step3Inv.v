(* StepInv.v's form of the invariant with Inv3.v's window fact (s3_head) in place of (A) (wbits = 0 ->
   wsize = 0): mwf3x = mwf + xwf3, equivalent to Inv3.v's mwf3 (Step5Mwf.mwf3x_iff).  The Step3*.v files
   prove the cases over it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.StepInv.
Import ListNotations.
Local Open Scope Z_scope.

Record xwf3 (m: mst) : Prop := {
  x3_head : m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 ->
            i_wsize (m_s m) = 0 /\ i_win (m_s m) = false;
  x3_lenext : m_mode m = LENEXT -> i_length (m_s m) <= 258;
  x3_distext : m_mode m = DISTEXT -> i_offset (m_s m) <= 32768;
  x3_lens : decode_mode (m_mode m) ->
            lvalid lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) }.

Record mwf3x (m: mst) : Prop := { m3_w : mwf m; m3_x : xwf3 m }.
